#ifndef HISTORYITEMWIDGET_H
#define HISTORYITEMWIDGET_H

#include <QFrame>

QT_BEGIN_NAMESPACE
namespace Ui {
class HistoryItemWidget;
}
QT_END_NAMESPACE

// A widget which contains a command issued in the past
// and its result.
class HistoryItemWidget: public QFrame {
    Q_OBJECT

public:
    // Sets the two labels with the parameters given.
    HistoryItemWidget(int id, const QString& command, const QString& result, QWidget* parent = nullptr);
    // The first one has 1 as its id, the second 2 etc.
    // For getting the index which has to be written into history[.],
    // we have to subtract this from the number of items.
    int getId() const {return id;};

protected:
    // This will emit the clicked() signal.
    virtual void mouseReleaseEvent(QMouseEvent* event) override;

private:
    Ui::HistoryItemWidget *ui;
    int id;

signals:
    void clicked();
};

#endif // HISTORYITEMWIDGET_H
