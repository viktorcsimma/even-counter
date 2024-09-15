#ifndef MAINWINDOW_H
#define MAINWINDOW_H

#include <QMainWindow>

#include "ViewModel/MainViewModel.hpp"

QT_BEGIN_NAMESPACE
namespace Ui {
class MainWindow;
}
QT_END_NAMESPACE

class MainWindow : public QMainWindow
{
    Q_OBJECT

public:
    MainWindow(MainViewModel& viewModel, QWidget *parent = nullptr);
    // This does _not_ destruct the view model; that is the task of the main function.
    ~MainWindow();

public slots:
    void enterClicked();
    void settingsButtonClicked();
    void preciseOutputButtonClicked();

private:
    Ui::MainWindow *ui;

    // The view model behind the window.
    // This refers to the same object throughout the entire existence of the window;
    // mode changes are achieved by changing the HsCalcStateWrapper instance under the view model.
    MainViewModel& viewModel;

    // Returns the number of current history items.
    int numberOfHistoryItems() const;
};
#endif // MAINWINDOW_H
